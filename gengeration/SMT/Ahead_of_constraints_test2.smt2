; SMTԼ�������B�Ƿ���A������Ҿ�����[range_x, range_x+5]��Χ��


; �������
(declare-const A_x Real)
(declare-const A_y Real)
(declare-const A_heading Real)
(declare-const B_x Real)
(declare-const B_y Real)
(declare-const range_x Real)


; ������ֵ֪
(assert (= A_x 0))
(assert (= A_y 0))
(assert (= A_heading 0))
(assert (= B_x 2.67857))
(assert (= B_y 15))


; ����������꣬B���A
(define-fun delta_x () Real (- B_x A_x))
(define-fun delta_y () Real (- B_y A_y))

; �������
(define-fun distance () Real (sqrt (+ (* delta_x delta_x) (* delta_y delta_y))))

; ����B�����X��Ļ��ȣ�ȡֵ��ΧΪ[-pi,pi]��
(define-fun angle_rad_x () Real (atan2 delta_y delta_x))

; �淶���� [0, 2��) ��Χ
(define-fun angle_rad_nom () Real
    (let ((raw_angle angle_rad_x))
        (ite (< raw_angle 0.0)
             (+ raw_angle (* 2.0 3.141592653589793))
             raw_angle)))

; ����B�����y��Ļ���
(define-fun angle_rad_y () Real (-  angle_rad_nom  (/ 3.141592653589793 2) ))

; ����B���A�Ļ���
(define-fun angle_rad () Real (- angle_rad_y A_heading))

; ת��Ϊ����
(define-fun angle_deg () Real (* angle_rad (/ 180.0 3.141592653589793)))

; ǰ���Ƕȷ�Χ��A_heading - 10�ȵ�A_heading + 10�ȣ�
(define-fun theta_left_min () Real (- A_heading 10.0))
(define-fun theta_left_max () Real (+ A_heading 10.0))

; �淶���Ƕȵ�[0, 360)
(define-fun normalize_angle ((theta Real)) Real
    (ite (>= theta 360.0) (- theta 360.0) theta))

(define-fun theta_left_min_norm () Real (normalize_angle theta_left_min))
(define-fun theta_left_max_norm () Real (normalize_angle theta_left_max))

; �Ƕ�Լ���������Խ0�ȵ������
(define-fun angle_constraint () Bool
    (ite (<= theta_left_min_norm theta_left_max_norm)
        (and (>= angle_deg theta_left_min_norm) (<= angle_deg theta_left_max_norm))
        (or (>= angle_deg theta_left_min_norm) (<= angle_deg theta_left_max_norm))))

; ����Լ��
(define-fun range_y () Real (+ range_x 5.0))
(define-fun distance_constraint () Bool
    (and (>= distance range_x) (<= distance range_y)))

; ��Լ��
(assert (and angle_constraint distance_constraint))

; ����������
(check-sat)
(get-model)
